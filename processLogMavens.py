#!/usr/bin/python
# processLogMavens.py
# Steve Grantz steve@degen.club
# 2020-04-26
# Usage:
# python processLogMavens.py logfile.txt [logfile2.txt ...]

############################################################################################################
# WHAT THIS DOES
#
# goal of this program is to process Poker Mavens logs to track player activity
# - initial appearance (initial buy-in)
# - addition of chips
# - last known amount of chips
#
# To do this we will take the logs and first break it up into hand by hand, indexed by time
# for a chronology
#
# Then we can loop through each hand, and process for player activity
# the first time we see a player, we add them and their first known chip count
# then in each hand we not additional chips, as well as resolution of the pot
#
# When processing the next hand, everything SHOULD align
# if it does not, throw an error
# otherwise keep processing
#
# look for wins, add ons, and pot contributions
# log cash in and cash out for narrative at end of night
#
# KEY ASSUMPTIONS
#
# assume unique hand number (that is the hand number can NOT repeat across tables)
# assume that the hand nummber structure NNN-M can be reduced to NNN andt hat the M local part is not needed
# configurable options can be specified in an INI file specified by a constant OPTIONS_FILE below
#
#
# CHANGE LOG
# 2020-04-26 v0.1 first version
# 2020-04-28 v0.2 email results
# 2020-05-12 v0.4 bug fixes
# 2020-05-15 v0.5 added glob work
# 2020-05-15 v0.6 incorporate suggested fixes for numeric formatting and text matching for names
# 2020-06-16 v0.7 move commonly changed options to an INI file loaded at run time
# 2020-06-17 v0.7.1 also support plain text export of emails with names from Mavens
# 2020-06-29 v0.7.2 change  skip prior option behavior to process multiple tables, files in any order
#

import argparse
import configparser
import csv
import datetime
import glob
import getpass
import json
import os
import re
import sys
# CC added import of debugger
# import pdb

from os import path
from smtplib import SMTP

# script level constants
# these are constants that are set in this script file and not intended to be edited or changed
VERSION = "0.7.2"
OPTIONS_FILE = "processLogMavens.ini"
DEBUGLEVEL = 0
LOCAL = "local"
INDEX = "index"
TEXT = "text"
FIRST = "first"
LATEST = "latest"
LAST = "last"
IN = "cash in"
OUT = "cash out"
WAITING = "sitting out"
LEFT = "left table"
NOTES = "notes"
TABLE="table"
COUNT="count"
DATETIME="datetime"
NAME="name"
UNIT="unit"
EMAIL="email"
EARLIEST="earliest"
STARTHANDS="start hands"
SKIPPED="skipped"

# constants for processing INI and setting configurable defaults
CSV_NOTE="CsvNote"
CSVTRANS="CsvTransactionsFile"
CSVBALANCE="CsvBalancesFile"
EMAIL_SUBJ_PREFIX = "EmailSubjectPrefix"
FROMADDRESS = 'EmailFromAdress'
CCADDRESS = 'EmailCcAddress'
SMTPSERVER = 'EmailSmtpServer'
SMTPPORT = 'EmailSmtpPort'
POSITIVE_STATE = "PositiveStateWords"
NEGATIVE_STATE = "NegativeStateWords"
ROSTER_FILE =  "RosterFile"
EMAIL_EXPORT_FILE = "EmailExportFile"
# end script level constants

# configurable constants
# these are constants that are meant to be configurable - they could be edited here,
# or specified in a configuration file that is external to this script and checked for at run time
# CSV and notes
DEFAULT_OPTIONS = {
    CSVBALANCE: "balances.csv",
    CSVTRANS: "gamelog.csv",
    CSV_NOTE: 'Python calculation of Poker Mavens session',
    POSITIVE_STATE: "is up",
    NEGATIVE_STATE: "is down",

    # constants around email options
    EMAIL_SUBJ_PREFIX: "Mavens game info from ",
    FROMADDRESS: 'me0@mydomain.tld',
    CCADDRESS: 'me@mydomain.tld',
    SMTPSERVER: 'mail.mydomain.tld',
    SMTPPORT: '26',

    # roster file
    ROSTER_FILE: 'roster.json'
}

# end configurable constants

##################################################################################################################
#
# DATA STRUCTURES
#
hands = {}    # the hands dictionary
              # structure
              # KEY - string - hand number
              # LOCAL - string - he "dash" portion of the hand number, may recombine, but so far unique without it
              # DATETIME - datetime - timestamp for the hand
              # TABLE - string - table where the hand happened
              # TEXT  - string - full text of hand, with newlines

players = {}  # the players dictionary
              # structure
              # KEY - string - player name as found in log
              # IN - float - total money in
              # OUT - float - total money out
              # NOTES - string log of activity with newlines
              # sub-dictionary by TABLE ******
              #      KEY - string for the table - will only exist if player was seen at table in logs
              #      FIRST - float - initial buy in for table - not really used much, could be deprecated
              #      IN - float - money in at this table
              #      OUT - float - money out at this table
              #      WAITING - Boolean - whether player is seated ut not in play
              #      LEFT - Boolean - player has been at table but is no longer seated
              #      LATEST - float - running tally of player holding at the table - IMPORTANT for checking consistency

tables = {}   # the tables dictionary
              # structure
              # KEY - string - table name as found in log
              # COUNT - integer - number of hands processed for table
              # SKIPPED - integer - number of hands skipped (if skip prior hands option in use)
              # STARTHANDS - Boolean flag to indicate if hands are being processed (True unless skip prior hands in use)
              # EARLIEST - datetime - the earliest time stamp for a hand processed for this table
              # LATEST - datetime - the latest time stamp for a hand processed for this table
              # LAST - string - hand number for the latest hand processed for this table
              #        LAST and LATEST are used to mark the "end" activity of players standing up
              #        they represent the last seen hand at the table from the processed logs

csvRows = []  # list of lists for the csv transaction content
              # see CSV Header for list of fields
              # CSV - log of activity in CS format - with newlines
csvHeader =  ["Time",
               "Table",
               "Hand Number",
               "Player",
               "Action",
               "Amount In",
               "Amount Out"
               ]

csvBalances = []  # list of lists for the csv balance content
csvBalanceHeader =  ["Date",
                     "Disposition",
                     "Player",
                     "Amount"
                     ]

# resolvedScreenNames dictionary takes in Poker Mavens Screen Name as has info needed for processing
# The preferred way of including this information is to populate an external JSON file and
# list that JSON file in the INI file using the RosterFile setting
#               Structure
#               KEY - Poker Mavens screen name
#               NAME - short name used in player ledger
#               EMAIL - email address for the player for sending player notes for session
resolvedScreenNames = {
               "MyScreenName":{"name":"me","email":"me@mydomain.tld"},
               }

# end of data structures
#
#######################################################################################################################

##################################################################################################################
#
# FUNCTIONS
#

# isNewPlayer checks to see if the player exists in the player dictionary, and if not, adds them
# ALL it does is add them and create initial notes, so if additional work needs to be done, check the
# return status for True and then do that extra work
# if context is given in the form of a table name, then additionally the function checks if the player
# has a sub-dictionary for the table. If not, that is created.
#
def isNewPlayer(check, table = None):
    "Check to see if player exists in players dictionary, and add them if not. Return new status."
    isNew = False
    if (table is not None):
        if (not check in players):
            isNew = True
            players[check] = {IN: 0, OUT: 0, NOTES: ""}
            players[player][NOTES] = ("Player Notes for " + player + os.linesep)
        if (not table in players[check]):
            isNew = True
            players[player][table] = {FIRST: 0, IN: 0, LATEST: 0, OUT: 0, LEFT: False}
    elif (not check in players):
        isNew = True
        players[check] = {IN: 0, OUT: 0, NOTES: ""}
        players[player][NOTES] = ("Player Notes for " + player + os.linesep)

    return isNew


# end of functions
#
#######################################################################################################################

lineCount = 0
sessionDate = datetime.datetime.now().strftime("%m/%d/%Y")
optionInformation = "Options read from " + OPTIONS_FILE

# look for configuration file and use those settings
# then load player roster if specified and found
# finally if there is an EmailExportFile specified, open that,
# parse each line, and either update or create a resolvedScreenName dictionary entry using
# the combination of ScreenName and email on each line of that file
# the export file format is that which Mavens produces from the
# Accounts tab "Export > Emails With Names" option
config = configparser.ConfigParser(defaults=DEFAULT_OPTIONS)
try:
    with open(OPTIONS_FILE,encoding="utf-8") as optionsFile:
        config.read_file(optionsFile)
        rosterFile = config.get('DEFAULT',ROSTER_FILE)
        try:
            with open(rosterFile,encoding="utf-8") as jsonRosterFile:
                resolvedScreenNames =  json.load(jsonRosterFile)
        except IOError:
            optionInformation += " Could not read rosterFile: " + rosterFile
        if (config.has_option('DEFAULT', EMAIL_EXPORT_FILE)):
            emailExportFile = config.get('DEFAULT', EMAIL_EXPORT_FILE)
            try:
                with open(emailExportFile,encoding="utf-8") as emailListHandler:
                    for line in emailListHandler:
                        matches = re.search("([\w-]+) <([^>]+)>", line)
                        if (matches != None):
                            screenName = matches.group(1)
                            email = matches.group(2)
                            if (screenName in resolvedScreenNames):
                                resolvedScreenNames[screenName][EMAIL] = email
                            else:
                                resolvedScreenNames[screenName] = {EMAIL: email}

            except IOError:
                optionInformation += "\nEmail text file specified but unable to open " + emailExportFile



except IOError:
    optionInformation = "Could not read " + OPTIONS_FILE + ". Using default values from script."


# get and parse command line arguments
# then process some key ones straight away
# namely, if roster option is used, dump the player roster and go
# if email option is activated, check for presence of password command line argument
# if not there prompt for it
parser = argparse.ArgumentParser(description=('Process Poker Mavens log files and deliver transaction info and player balances. v'
                                              + VERSION))
parser.add_argument('-c','--csv', action="store_true",dest="doCsv",default=False,help="Output CSV content.")
parser.add_argument('-e','--email', action="store_true",dest="doEmail",default=False,help="Email player results.")
parser.add_argument('-g','--glob', action="append",dest="fileglob",
                    help="Pass a file-matching pattern for pathname expansion. Process each filename matching the expansion.")
parser.add_argument('-p','--password', action="store",dest="password",
                    help=("Password for email account (" + config.get('DEFAULT',FROMADDRESS) + ")"))
parser.add_argument('-q','--quiet', action="store_true",dest="quiet",default=False,help="Run in quiet mode with minimal output.")
parser.add_argument('-r','--roster', action="store_true",dest="roster",default=False,
                    help="Show roster of players known to the script and exit.")
parser.add_argument('file', type=argparse.FileType('r'), nargs='*',help="plain text files of Poker Mavens hand histories to process.")
# CC Added skip argument to allow user to skip over prior day's hands in first log file. default is NOT to skip anything
# so start counting hands immediately (same output as before without this option)
parser.add_argument('-s','--skip-prior-hands', action="store_true",dest="skipPriorHands",default=False,
                    help="Skip hands for tables until local hand count reads number one. Intended to find overnight session divide.")
args = parser.parse_args()

if (args.roster):
    if (args.doCsv):
        print("Poker Mavens Screen Name,Nickname,EMail")
    else:
        print("Roster of Players: " + str(len(resolvedScreenNames)))
        print("")
    for player in sorted(resolvedScreenNames.keys(), key=str.casefold):
        name = ''
        if (NAME in resolvedScreenNames[player]):
            name = resolvedScreenNames[player][NAME]
        if (args.doCsv):
            text = (player + "," + name + ",")
            if (EMAIL in resolvedScreenNames[player]):
                text = text + resolvedScreenNames[player][EMAIL]
        else:
            text = (player + " (" + name + ")")
            if (EMAIL in resolvedScreenNames[player]):
                text = text + " - " + resolvedScreenNames[player][EMAIL]
        print (text)
    sys.exit(0)

emailPassword = ''
if(args.doEmail):
    if (args.password is None):
        emailPassword = getpass.getpass("Enter the password for the email account (" + config.get('DEFAULT',FROMADDRESS) +"): ")
    else:
        emailPassword = args.password

lastHandTime = datetime.datetime.now()

# get the files to process
# they either came in from the command line as individual file name arguments passed to args.file
# or as pathname patterns passed to a --glob option
filesToProcess = []
for fh in args.file:
    filesToProcess.append(fh.name)
    fh.close()

if (args.fileglob is not None):
    for g in args.fileglob:
        expansion = glob.glob(g)
        for pathname in expansion:
            filesToProcess.append(pathname)

numFiles = len(filesToProcess)
if (numFiles == 0):
    print("Must provide a name of a log file to process.")
else:
    # process each file listed on the command line
    # first loop through is just to parse and get each hand separated, and get basic hand
    # info into the hands dictionary
    # basic hand info is hand number, local hand number, hand time, and table
    # everything else goes into TEXT
    
    # Added startHands variable to track when to start adding hands
    # mark each table with startHands
    # if skipPriorHands is true, then startHands will be false
    # otherwise this is going to be true
    # this is then used int eh next loop to determine when to start processing hands
    startHands = not args.skipPriorHands
    
    for filename in filesToProcess:
        f = open(filename, mode='r', encoding='utf-8')
        handNumber = None
        handTime = None
        line = f.readline()
        while (len(line) != 0):
            matches = re.search("Hand #(\d*)-(\d*) - (.*)$",line)
            if (matches != None):
                handNumber = matches.group(1)
                localHandNumber = matches.group(2)
                handTime = datetime.datetime.strptime(matches.group(3),"%Y-%m-%d %H:%M:%S")
                hands[handNumber] = {LOCAL: localHandNumber,
                                   DATETIME: handTime,
                                   TEXT: ''}
            elif (handNumber is not None):
                table = re.search("Table: (.*)$", line)
                if (table != None):
                    tableName = table.group(1)
                    if (not tableName in tables):
                        tables[tableName] = {COUNT: 0,
                                             EARLIEST: None,
                                             LAST: "",
                                             STARTHANDS: startHands,
                                             SKIPPED: 0}
                    hands[handNumber][TABLE] = tableName
                hands[handNumber][TEXT] = hands[handNumber][TEXT] + line
            line = f.readline()
        f.close()

    handNumber = ""
    handTime = datetime.datetime.now()

    # now that we have all hands from all the files,
    # use the timestamps of the imported hands to process them in chronological order
    # this is the place for processing the text of each hand and look for player actions
    # we need to find the first hand to start to process. if the user told us to ignore the prior day,
    # then we will skip over the first hands until the local hand number is reset to 1.
    # we'll use the startTable variable to control when to actually start adding the hands
    # and that is possibly different for each table, so we need to look it up for the table for this hand
    for handNumber in sorted(hands.keys(), key=lambda hand: hands[hand][DATETIME] ):
        # print(handNumber) #DEBUG
        handTime = hands[handNumber][DATETIME]
        table = hands[handNumber][TABLE]
        localHandNumber = hands[handNumber][LOCAL]
        startTable = tables[table][STARTHANDS]

        if (not startTable):
            if (localHandNumber != "1"):
                tables[table][SKIPPED] += 1
                continue
            else:
                tables[table][EARLIEST] = handTime
                tables[table][STARTHANDS] = True

        tables[table][COUNT] += 1
        tables[table][LAST] = handNumber
        tables[table][LATEST] = handTime
        lastHandTime = handTime
        if (tables[table][EARLIEST] is None):
            tables[table][EARLIEST] = handTime
        # print(handTime) # DEBUG

        for line in hands[handNumber][TEXT].splitlines():
            # the text match to look for a seated player and see their chip amount
            seat = re.search("Seat \d+: ([\w-]+) \(([\d.]+)\)",line)
            if (seat != None):
                player = seat.group(1)
                stack = float(seat.group(2))

                if (isNewPlayer(check=player, table=table)):
                    players[player][IN] += stack
                    players[player][table][IN] = stack
                    players[player][table][FIRST] = stack
                    players[player][table][LATEST] = stack
                    players[player][NOTES] = players[player][NOTES] + (str(handTime) +
                                              " table " + table +
                                              " hand (" + handNumber + ") " +
                                              "initial buy in " + "{0:.2f}".format(stack) + os.linesep)
                    csvRows.append([handTime,table,handNumber,player,"initial buy in",stack,""])
                else:
                    # check for consistent state of chips from last hand
                    # this is where we find corner cases and so on
                    # found split pot issue, side pot issue by virtue of having this consistency check
                    # NOTE - if player was waiting the stack may have changed,
                    #        so adjust accordingly and log it
                    if (players[player][table][LATEST] != stack):
                        if (players[player][table][WAITING] or players[player][table][LEFT]):
                            if (stack > players[player][table][LATEST]):
                                adjustment = stack - players[player][table][LATEST]
                                if ("{0:.2f}".format(adjustment) != "0.00"):
                                    players[player][table][LATEST] = stack
                                    players[player][table][IN] += adjustment
                                    players[player][IN] += adjustment
                                    action = "player returned with " if (players[player][table][LEFT]) else "while waiting added on by "
                                    players[player][NOTES] = (players[player][NOTES] + str(handTime) + " table " + table +
                                            " hand (" + handNumber + ") " + action + "{0:.2f}".format(adjustment) + os.linesep)
                                    csvRows.append([handTime,table,handNumber,player,"add on while waiting",adjustment,""])
                            else:
                                adjustment = players[player][table][LATEST] - stack
                                if ("{0:.2f}".format(adjustment) != "0.00"):
                                    players[player][table][LATEST] = stack
                                    players[player][table][OUT] += adjustment
                                    players[player][OUT] += adjustment
                                    players[player][NOTES] = (players[player][NOTES] + str(handTime) + " " + table + " hand (" + handNumber + ") " +
                                            "while waiting reduced by " + "{0:.2f}".format(adjustment) + os.linesep)
                                    csvRows.append([handTime,table,handNumber,player,"reduction while waiting","",adjustment])
                        else:
                            if ("{0:.2f}".format(stack) != "{0:.2f}".format(players[player][table][LATEST])):
                                print("Inconsistent state for " + player + " in table " + table + " hand " + handNumber + " has " + str(stack) +
                                        " expected " + "{0:.2f}".format(players[player][table][LATEST]))
                                action = ''
                                adjustment = 0
                                if (stack > players[player][table][LATEST]):
                                    adjustment = stack - players[player][table][LATEST]
                                    if ("{0:.2f}".format(adjustment) != "0.00"):
                                        players[player][table][LATEST] = stack
                                        players[player][table][IN] += adjustment
                                        players[player][IN] += adjustment
                                        action = "adjusting for consistency - adding on "
                                else:
                                    adjustment = players[player][table][LATEST] - stack
                                    if ("{0:.2f}".format(adjustment) != "0.00"):
                                        players[player][table][LATEST] = stack
                                        players[player][table][OUT] += adjustment
                                        players[player][OUT] += adjustment
                                        action = "adjusting for consistency - deducting "

                                if ("{0:.2f}".format(adjustment) != "0.00"):
                                    players[player][NOTES] = (players[player][NOTES] + str(handTime) + " table " + table +
                                            " hand (" + handNumber + ") " + action + "{0:.2f}".format(adjustment) + os.linesep)
                                    csvRows.append([handTime,table,handNumber,player,action,adjustment,""])

                # player is active at this table, so mark the LEFT attribute for the tabe as False
                players[player][table][LEFT] = False

                # change state on sitting or waiting
                if (re.search(r'sitting',line) or re.search(r'waiting',line)):
                    players[player][table][WAITING] = True
                else:
                    players[player][table][WAITING] = False

            # the text to match for an add on
            addOn = re.search("([\w-]+) adds ([\d.]+) chip",line)
            if (addOn != None):
                player = addOn.group(1)
                additional = float(addOn.group(2))
                if (isNewPlayer(check=player,table=table)):
                    players[player][NOTES] = (players[player][NOTES] + str(handTime) + " table " + table +
                                              " hand (" + handNumber + ") " +
                                              "joined by add-on "  +os.linesep)
                players[player][IN] += additional
                players[player][table][IN] += additional
                players[player][table][LATEST] += additional
                players[player][NOTES] = (players[player][NOTES] + str(handTime) + " table " + table +  " hand (" + handNumber + ") " +
                        "added on " + "{0:.2f}".format(additional) + os.linesep)
                csvRows.append([handTime,table,handNumber,player,"add on",additional,""])


            # the text to check for a win
            winner = re.search("([\w-]+) (wins|splits).*Pot *\d? *\(([\d.]+)\)",line)
            if (winner != None):
                player = winner.group(1)
                win = float(winner.group(3))
                players[player][table][LATEST] += win

            # find contributions to the pot
            # this is a series of contributions of the form "PlayerName: Amount" separated by commas
            # needed for updating the LATEST amount on this table for each player, for consistency check next hand
            pot = re.search("Rake.*Pot.*Players \((.*)\)", line)
            if (pot != None):
                potString = pot.group(1)
                for contribution in potString.split(","):
                    (player,amount) = contribution.split(":")
                    player = player.strip()
                    players[player][table][LATEST] -= float(amount)

        # end of for loop, loop through active players and see if anyone has left the table -
        # if so, register a cash out and also mark the player as having LEFT the table
        for player in players.keys():
            seatSearch = r"Seat \d+: " + re.escape(player)
            if (not re.search(seatSearch, hands[handNumber][TEXT])):
                if (table in players[player] and not players[player][table][LEFT]):
                    amount = players[player][table][LATEST]
                    players[player][OUT] += amount
                    players[player][table][OUT] += amount
                    players[player][table][LATEST] = 0
                    players[player][table][WAITING] = True
                    players[player][NOTES] = (players[player][NOTES] + str(handTime) + " table " + table + " hand (" + handNumber + ") " +
                            "stood up with " + "{0:.2f}".format(amount) + os.linesep)
                    csvRows.append([handTime,table,handNumber,player,"stood up with","",amount])
                    players[player][table][LEFT] = True



# SUMMARIZE
# note how many unique players
# note how many hands processed for each table
# then for each table, and each player, find out who was still listed as not left and mark them
# as left and what they stood up with

print(optionInformation)
print("Files: " + str(numFiles))
print("Players: " + str(len(players)))
for table in tables:
    print("Table " + table + ": Processed hands: " + str(tables[table][COUNT]))
    print("      " + table + ": Earliest hand: " + str(tables[table][EARLIEST]))
    print("      " + table + ": Latest hand: " + str(tables[table][LATEST]))
    if (args.skipPriorHands):
        print("      " + table + ": Skipped hands: " + str(tables[table][SKIPPED]))

    for player in players.keys():
        # done processing the hands, so get players up from the table
        if (table in players[player] and not players[player][table][LEFT]):
            amount = players[player][table][LATEST]
            players[player][OUT] += amount
            players[player][table][OUT] += amount
            players[player][table][LATEST] = 0
            players[player][table][LEFT] = True
            players[player][NOTES] = (players[player][NOTES] + str(tables[table][LATEST]) + " table " + table +
                                      " hand (" + tables[table][LAST] + ") " +
                                      "ended table with " + "{0:.2f}".format(amount) + os.linesep)
            csvRows.append([tables[table][LATEST],table,tables[table][LAST],player,"ended table with","",amount])

netBalance = 0

# separator
print("")

if (lastHandTime is not None):
    sessionDate = lastHandTime.strftime("%m/%d/%Y")

note = config.get('DEFAULT',CSV_NOTE)

for player in players.keys():
    # final tally
    cashIn = players[player][IN]
    cashOut = players[player][OUT]
    disposition=''
    diff = 0
    alias = player
    if (player in resolvedScreenNames and NAME in resolvedScreenNames[player]):
        alias = resolvedScreenNames[player][NAME]
    players[player][NOTES] = (players[player][NOTES] + "Total IN " + "{0:.2f}".format(cashIn) + os.linesep)
    players[player][NOTES] = (players[player][NOTES] + "Total OUT " + "{0:.2f}".format(cashOut) + os.linesep)
    if (cashIn == cashOut):
        players[player][NOTES] = (players[player][NOTES] +  player + ' breaks even.' + os.linesep)
        disposition = config.get('DEFAULT',POSITIVE_STATE)
    elif (cashIn > cashOut):
        diff = cashIn - cashOut
        netBalance += diff
        players[player][NOTES] = (players[player][NOTES] +  player + " " +
                                  config.get('DEFAULT',NEGATIVE_STATE) + " " + "{0:.2f}".format(diff) + os.linesep)
        disposition = config.get('DEFAULT',NEGATIVE_STATE)
    elif (cashIn < cashOut):
        diff = cashOut - cashIn
        netBalance -= diff
        players[player][NOTES] = (players[player][NOTES] +  player + " " +
                                  config.get('DEFAULT',POSITIVE_STATE) + " " + "{0:.2f}".format(diff) + os.linesep)
        disposition = config.get('DEFAULT',POSITIVE_STATE)

    csvBalances.append([sessionDate,disposition,alias,diff,note])



    if(not args.quiet):
        print(players[player][NOTES])
        print("")

print("Net balance: " + "{0:.2f}".format(netBalance))

if (args.doCsv):
    # Output CSV file of transactions
    with open(config.get('DEFAULT',CSVTRANS), 'w', encoding="utf-8", newline='') as csvfile:
        logwriter = csv.writer(csvfile, quoting=csv.QUOTE_MINIMAL)
        logwriter.writerow(csvHeader)
        for row in csvRows:
            logwriter.writerow(row)

        csvfile.close()
        print("CSV content written to " + config.get('DEFAULT',CSVTRANS))

    # Output CSV file of balances
    with open(config.get('DEFAULT',CSVBALANCE), 'w', encoding="utf-8", newline='') as csvfile:
        logwriter = csv.writer(csvfile, quoting=csv.QUOTE_MINIMAL)
        logwriter.writerow(csvBalanceHeader)
        for row in csvBalances:
            logwriter.writerow(row)

        csvfile.close()
        print("CSV balance content written to " + config.get('DEFAULT',CSVBALANCE))

if (args.doEmail):
    smtp = SMTP()

    cc_addr = config.get('DEFAULT',CCADDRESS)
    from_addr = config.get('DEFAULT',FROMADDRESS)

    smtp.set_debuglevel(DEBUGLEVEL)
    smtp.connect(config.get('DEFAULT',SMTPSERVER), config.getint('DEFAULT',SMTPPORT))
    smtp.login(from_addr, emailPassword)
    #TODO: error handling for a failed login to SMTP server


    date = datetime.datetime.now().strftime("%a, %d %b %Y %T %z (%Z)")
    emailCount = 0


    for player in players:
        subj = config.get('DEFAULT',EMAIL_SUBJ_PREFIX) + " " + sessionDate
        if (player in resolvedScreenNames and EMAIL in resolvedScreenNames[player]):
            emailCount += 1
            recipients = [cc_addr]
            to_addr = resolvedScreenNames[player][EMAIL]
            recipients.append(to_addr)

            subj = subj + " for " + player 
            message_text = players[player][NOTES]

            msg = ("From: %s\nTo: %s\nCC: %s\nSubject: %s\nDate: %s\n\n%s"
                   % (from_addr, to_addr, cc_addr, subj, date, message_text))

            smtp.sendmail(from_addr, recipients, msg.encode("utf-8"))
    smtp.quit()
    print("Email messages sent: " + str(emailCount))
