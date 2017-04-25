#! /usr/bin/python3

import sys
import time
import threading
import select
import signal
import fcntl
import os
import socket
import struct
import math
import argparse
import functools
from gpiozero import MCP3008
# import pdb

SPI_PORT = 0
SPI_DEVICE = 0

DEF_PORT = 10000
RECV_BUFSIZ = 4096
PROTO_VER = 1
PROTO_AUTHTYPE_NONE = 1
PROTO_UNUSED = 0
PROTO_HDRSIZ = 4
PROTO_CMD_GETLAST = 1
PROTO_CMD_RETLAST = 2

MIB_BASE = '.1.3.6.1.3.999'
MIB_DEVTYPE_MCP3008 = 1 # ADC device type of Analog Devices MCP3008
MIB_MAX_ACCESS_NA = 0   # not-accessible
MIB_MAX_ACCESS_AN = 1   # accessible-for-notify
MIB_MAX_ACCESS_RO = 2   # read-only
MIB_MAX_ACCESS_RW = 3   # read-write
MIB_MAX_ACCESS_RC = 4   # read-create
MIB_SYNTAX_INT = 1      # INTEGER (or Integer32)
MIB_SYNTAX_STRING = 2   # OCTET STRING
MIB_SYNTAX_OID = 3      # OBJECT IDENTIFIER
MIB_SYNTAX_BITS = 4     # BITS construct
MIB_SYNTAX_IP = 5       # IpAddress
MIB_SYNTAX_COUNT = 6    # Counter32
MIB_SYNTAX_GAUGE = 7    # Gauge32
MIB_SYNTAX_TT = 8       # TimeTicks
MIB_SYNTAX_COUNT64 = 9  # Counter64
MIB_SYNTAX_UINT = 10    # Unsigned32
MIB_SYNTAX_SEQ = 11     # SEQUENCE
MIB_SYNTAX_NAMES = {
    MIB_SYNTAX_INT: 'integer',
    MIB_SYNTAX_STRING: 'string',
    MIB_SYNTAX_OID: 'objectid',
    MIB_SYNTAX_BITS: 'integer',
    MIB_SYNTAX_IP: 'ipaddress',
    MIB_SYNTAX_COUNT: 'counter',
    MIB_SYNTAX_GAUGE: 'gauge',
    MIB_SYNTAX_TT: 'timeticks',
    MIB_SYNTAX_COUNT64: 'counter',
    MIB_SYNTAX_UINT: 'integer',
    MIB_SYNTAX_SEQ: 'string'
}

VREF = 3324     # voltage reference fed into VREF (pin 15) of MCP3008, in mV
R_PU = 9920     # pull-up resistor of voltage divider, in Ohms
R_PD = 9930     # pull-down resistor of voltage divider, in Ohms

DEF_AVG_SAMPLES = 5     # default number of samples taken out of each channel
DEF_AVG_DELTA = .001    # default delta between samples, in seconds
DEF_FACTOR = 1          # default scale factor for channel data
MIN_AVG_SAMPLES = 1     # minimal number of number of samples
MIN_AVG_DELTA = 0       # minimal delta between samples

DEF_MEASURE_INT = 10                    # default interval between measurements, in seconds
MIVAL_SHIFT = .1                        # constant time shift subtracted from calculated start time of measurement circle, in seconds
TS_FORMAT = '%Y-%m-%d %H:%M:%S'         # output date/time format
DEBUG_TS_FORMAT = '%Y-%m-%d %H:%M:%S'   # output date/time format for debug output

SIG_WAKEUP_FD_RLEN = 8  # length of data read from signal wakeup file descriptor

channels_conf = {   # MCP3008 channels list
    0: 'MAIN',
    1: 'REG',
    2: 'BAT',
    3: '+5V'
}

mib = {}
oids = []

###
### Debug output
###
def dbg(message):
    if debug:
        caller = sys._getframe(1).f_code.co_name
        ts = time.time()
        ts_string = time.strftime(DEBUG_TS_FORMAT, time.localtime(ts))
        ts_fraction = int(round(math.modf(ts)[0], 3) * 1000)
        debug_fileobj.write('DEBUG: {}.{:03d}: {}: {}\n'.format(ts_string, ts_fraction, caller, message))
        debug_fileobj.flush()

###
### MIB var record
###

class MIBVar:

    # Constructor
    def __init__(self, name, oid, handler=lambda: None, max_access=MIB_MAX_ACCESS_RO, syntax=MIB_SYNTAX_STRING,
        timeticks_conv=False):

        # Class variables
        self._name = name               # name
        self._oid = oid                 # OID (relative to MIB_BASE)
        self._next_oid = None           # OID of next MIBVar object (needed for GETNEXT SNMP request)
        self._handler = handler         # handler function for processing of GET SNMP equest
        self._max_access = max_access   # access type of MIBVar
        self._syntax = syntax           # syntax of MIBVar object
        self._timeticks_conv = timeticks_conv   # timeticks conversion indicator

    # Return name
    def get_name(self):
        return self._name

    # Return OID
    def get_oid(self):
        return self._oid

    # Return OID of next MIB variable
    def get_successor(self):
        return self._next_oid

    # Return MAX-ACCESS property
    def get_max_access(self):
        return self._max_access

    # Return SYNTAX property
    def get_syntax(self):
        return self._syntax

    # Return MIB value
    def get_value(self):
        if not self._handler or self._max_access < MIB_MAX_ACCESS_RO:
            return None
        else:
            val = self._handler()
            if self._syntax == MIB_SYNTAX_TT and self._timeticks_conv:
                val = round(val * 100)
            return val

    # Set OID of next MIB variable
    def set_successor(self, oid):
        self._next_oid = oid

###
### Compare two OIDs, return -1, 0, 1 or None in case of wrong format
###
def cmp_oids(oid1, oid2):

    # Strip leading and trailing dots, split to lists
    list1 = oid1.strip('.').split('.')
    list2 = oid2.strip('.').split('.')

    # Loop synchronously through the both lists until one of them ends
    while len(list1) and len(list2):

        # Shift first elements from lists
        e1 = list1.pop(0)
        e2 = list2.pop(0)

        # Replace empty strings with zero
        if not e1:
            e1 = '0'
        if not e2:
            e2 = '0'

        # Check for non digits
        if not e1.isdigit() or not e2.isdigit():
            return None

        # Convert to integer and compare elements
        i1 = int(e1)
        i2 = int(e2)
        if i1 < i2:
            return -1
        elif i1 > i2:
            return 1

    # Compare length of the both lists
    if len(list1):
        return 1
    elif len(list2):
        return -1
    else:
        return 0

###
### Init MIB and list of OIDs
###
def mib_init(ch_list):
    global mib, oids

    # Base tree
    mib[''] = MIBVar('snGroup', '', max_access=MIB_MAX_ACCESS_NA, syntax=MIB_SYNTAX_OID)

    # ADC tree
    mib['.1'] = MIBVar('snAdc', '.1', max_access=MIB_MAX_ACCESS_NA, syntax=MIB_SYNTAX_OID)

    # Devices table
    mib['.1.1.0'] = MIBVar('snAdcDevNumber', '.1.1.0', handler=lambda: 1, syntax=MIB_SYNTAX_INT)
    mib['.1.2'] = MIBVar('snAdcDevTable', '.1.2', max_access=MIB_MAX_ACCESS_NA, syntax=MIB_SYNTAX_OID)
    mib['.1.2.1'] = MIBVar('snAdcDevEntry', '.1.2.1', max_access=MIB_MAX_ACCESS_NA, syntax=MIB_SYNTAX_OID)
    p = '.1.2.1.'
    # MCP3008 on PCB
    s = '.1'
    o = p + str(1) + s
    mib[o] = MIBVar('devSpiPort', o, handler=lambda: SPI_PORT, syntax=MIB_SYNTAX_INT)
    o = p + str(2) + s
    mib[o] = MIBVar('devSpiDevice', o, handler=lambda: SPI_DEVICE, syntax=MIB_SYNTAX_INT)
    o = p + str(3) + s
    mib[o] = MIBVar('devType', o, handler=lambda: MIB_DEVTYPE_MCP3008, syntax=MIB_SYNTAX_INT)
    o = p + str(4) + s
    mib[o] = MIBVar('devName', o, handler=lambda: 'MCP3008 on PCB', syntax=MIB_SYNTAX_STRING)
    o = p + str(5) + s
    mib[o] = MIBVar('devChanNumber', o, handler=lambda: len(channels_conf), syntax=MIB_SYNTAX_INT)

    # Statistics Table
    mib['.1.3.0'] = MIBVar('snAdcStatsNumber', '.1.3.0', handler=lambda: 1, syntax=MIB_SYNTAX_INT)
    mib['.1.4'] = MIBVar('snAdcStatsTable', '.1.4', max_access=MIB_MAX_ACCESS_NA, syntax=MIB_SYNTAX_OID)
    mib['.1.4.1'] = MIBVar('snAdcStatsEntry', '.1.4.1', max_access=MIB_MAX_ACCESS_NA, syntax=MIB_SYNTAX_OID)
    p = '1.4.1.'
    # Single statistics block
    s = '.1'
    o = p + str(1) + s
    mib[o] = MIBVar('statsValid', o, handler=ch_list.valid, syntax=MIB_SYNTAX_INT)
    o = p + str(2) + s
    mib[o] = MIBVar('statsTsStart', o, handler=ch_list.ts_start, syntax=MIB_SYNTAX_TT, timeticks_conv=True)
    o = p + str(3) + s
    mib[o] = MIBVar('statsTsComplete', o, handler=ch_list.ts_complete, syntax=MIB_SYNTAX_TT, timeticks_conv=True)

    # Channels table
    mib['.1.5.0'] = MIBVar('snAdcChanNumber', '.1.5.0', handler=ch_list.num_of_channels, syntax=MIB_SYNTAX_INT)
    mib['.1.6'] = MIBVar('snAdcChanTable', '.1.6', max_access=MIB_MAX_ACCESS_NA, syntax=MIB_SYNTAX_OID)
    mib['.1.6.1'] = MIBVar('snAdcChanEntry', '.1.6.1', max_access=MIB_MAX_ACCESS_NA, syntax=MIB_SYNTAX_OID)
    p = '.1.6.1.'
    # Single channels block
    s = '.1.1.'
    for i in ch_list.sorted_ch_nums():
        ch_instance = ch_list.vec(i)
        s1 = s + str(i + 1)
        o = p + str(1) + s1
        mib[o] = MIBVar('chanNumber', o, handler=ch_instance.get_num, syntax=MIB_SYNTAX_INT)
        o = p + str(2) + s1
        mib[o] = MIBVar('chanName', o, handler=ch_instance.get_label, syntax=MIB_SYNTAX_STRING)
        o = p + str(3) + s1
        mib[o] = MIBVar('chanValid', o, handler=ch_instance.get_valid, syntax=MIB_SYNTAX_INT)
        o = p + str(4) + s1
        mib[o] = MIBVar('chanLast', o, handler=ch_instance.get_last, syntax=MIB_SYNTAX_GAUGE)
        o = p + str(5) + s1
        mib[o] = MIBVar('chanTs', o, handler=ch_instance.get_ts, syntax=MIB_SYNTAX_TT, timeticks_conv=True)

    # Make sorted list of OIDs
    oids = sorted(mib.keys(), key=functools.cmp_to_key(cmp_oids))

    # Fill in next OIDs
    for i, o in enumerate(oids[:-1]):
        mib[o].set_successor(oids[i + 1])

###
### Test full OID if it fits under MIB base
### If so return stripped OID or None otherwise
###
def strip_full_oid(full_oid):

    # Set default return value
    ret = None

    # Strip MIB base
    if full_oid.find(MIB_BASE) == 0:
        oid = full_oid[len(MIB_BASE):]

        # Test for stripped OID is legal (empty or begins with dot)
        if len(oid) == 0 or oid[0] == '.':
            ret = oid

    return ret

###
### Find MIBVar object by OID
### Return MIBVar object or None in the case of OID not exist
###
def find_mibvar(full_oid, mib):

    # Strip MIB base
    oid = strip_full_oid(full_oid)
    if oid is None:
        return None

    # Get MIBVar object by OID, it'll be None if not existed
    mibvar = mib.get(oid)
    return mibvar

###
### Find next accessible MIBVar object by OID
### Return MIBVar object or None in the case of next OID not exist
###
def find_mibvar_next(full_oid, mib, oids):

    # Strip MIB base
    oid = strip_full_oid(full_oid)
    if oid is None:
        return None

    # Try to get MIBVar object by given OID
    existed = mib.get(oid)

    # If MIBVar object with given OID exist then candidate object is its successor
    if existed:
        candidate = existed.get_successor()

    # If MIBVar object with given OID not existed ...
    else:

        # If given OID is lesser than first OID in current list then candidate object is the first one
        if cmp_oids(oid, oids[0]) < 0:
            candidate = mib.get(oids[0])

        # If given OID is greater than last OID in current list then there are no objects next to the last one, return None
        elif cmp_oids(oid, oids[-1]) > 0:
            return None

        # Run binary search for finding candidate object
        else:
            p_low = 0
            p_high = len(oids) - 1
            p_delta = p_high - p_low
            while p_delta > 1:
                p_check = p_low + int(p_delta / 2)
                if cmp_oids(oid, oids[p_check]) < 0:
                    p_high = p_check
                else:
                    p_low = p_check
                p_delta = p_high - p_low
            candidate = mib.get(oids[p_high])

    # The first accessible OID in chain of successors starting from candidate is next OID
    while candidate and mib[candidate].get_max_access() < MIB_MAX_ACCESS_RO:
        candidate = mib[candidate].get_successor()

    return mib.get(candidate)

###
### Channel record
###

class Channel:

    # Constructor
    def __init__(self, num=None, label=''):

        # Class variables
        self._num = num         # channel number on MCP3008
        self._label = label     # symbolic channel name
        self._adc = None        # instance of MCP3008 class
        self._acc = 0           # accumulator for consecutive measurements
        self._samples = 0       # current number of samples in one measurement circle
        self._valid = False     # valid flag
        self._last = None       # last calculated average value
        self._ts = None         # timestamp of last calculation

        self._adc = MCP3008(channel=self._num, port=SPI_PORT, device=SPI_DEVICE)

    # Reset accumulator
    def reset_acc(self):
        self._acc = 0
        self._samples = 0

    # Read current value and add it to accumulator
    def add_acc(self):
        self._acc += self._adc.value
        self._samples += 1

    # Calculate average of accumulator and store it
    def avg_acc(self, factor=1):
        self._valid = False
        self._last = round(self._acc * factor / self._samples)
        self._ts = time.time()
        self._valid = True

    # Return last value and its properties (valid indicator and timestamp)
    def get_lastprop(self):
        return self._valid, self._last, self._ts

    # Return channel number
    def get_num(self):
        return self._num

    # Return channel label
    def get_label(self):
        return self._label

    # Return last value
    def get_last(self):
        return self._last

    # Return valid indicator
    def get_valid(self):
        return self._valid

    # Return timestamp
    def get_ts(self):
        return self._ts

    # Clean-up
    def destroy(self):
        self._adc.close()

###
### Channel list record
###

class ChannelList:

    # Constructor
    def __init__(self, samples=DEF_AVG_SAMPLES, delta=DEF_AVG_DELTA, factor=DEF_FACTOR):

        # Class variables
        self._vec = {}                  # instances of Channel class
        self._sorted_ch_nums = []       # sorted list of channel numbers
        self._samples = DEF_AVG_SAMPLES # number of samples in one measurement circle
        self._delta = DEF_AVG_DELTA     # interval between consecutive measurements in one circle
        self._factor = DEF_FACTOR       # coefficient
        self._valid = False             # valid flag
        self._ts_start = None           # timestamp of starting of last measurement circle
        self._ts_complete = None        # timestamp of completing of last measurement circle
        self._lock = None               # locked when measurement circle runs
        self._last_values = {}          # last values

        self.set_parms(samples=samples, delta=delta, factor=factor)
        self._lock = threading.Lock()

    # Check and set parameters
    def set_parms(self, samples=None, delta=None, factor=None):
        if samples and type(samples).__name__ == 'int' and samples > MIN_AVG_SAMPLES:
            self._samples = samples
        if delta and (type(delta).__name__ in ['int', 'float']) and delta > MIN_AVG_DELTA:
            self._delta = delta
        if factor and (type(factor).__name__ in ['int', 'float']):
            self._factor = factor

    # Add channel to list
    def add_ch(self, num=None, label=''):
        if type(num).__name__ == 'int' and num in range(0, 8) and num not in self._vec.keys():
            self._vec[num] = Channel(num=num, label=label)
            self._sorted_ch_nums = sorted(self._vec.keys())
            self._last_values[num] = self._vec[num].get_lastprop()
            return 0
        else:
            return -1

    # Remove channel from list
    def rem_ch(self, num=None):
        if type(num).__name__ == 'int' and num in self._vec.keys():
            self._vec[num].destroy()
            del self._vec[num]
            self._sorted_ch_nums = sorted(self._vec.keys())
            del self._last_values[num]
            return 0
        else:
            return -1

    # Reset all channel accumulators
    def reset(self):
        for ch in self._sorted_ch_nums:
            self._vec[ch].reset_acc()

    # Read all channels
    def read(self):
        for ch in self._sorted_ch_nums:
            self._vec[ch].add_acc()

    # Calculate average value for all channels and load its
    def average(self):
        for ch in self._sorted_ch_nums:
            self._vec[ch].avg_acc(factor=self._factor)
            self._last_values[ch] = self._vec[ch].get_lastprop()

    # Measure circle
    def measure(self):

        # Acquire lock (nonblocking)
        if self._lock.acquire(blocking=False):
            try:

                # Reset valid flag, save starting timestamp, reset all channel accunulators
                self._valid = False
                self._ts_start = time.time()
                self.reset()

                # Start measurement circle
                i = self._samples
                while i:

                    # Read all channels
                    self.read()

                    # Decrement iteration counter and sleep-or-avg_and_break
                    i -= 1
                    if i:
                        time.sleep(self._delta)
                    else:
                        self.average()
                        break

            finally:

                # Set valid flag, save final timestamp and release lock
                self._ts_complete = time.time()
                self._valid = True
                self._lock.release()
                return 0
        else:
            return -1

    # Return last values
    def last(self):
        return self._valid, self._ts_start, self._ts_complete, self._last_values

    # Return number of channels
    def num_of_channels(self):
        return len(self._sorted_ch_nums)

    # Return sorted list of channel numbers
    def sorted_ch_nums(self):
        return self._sorted_ch_nums

    # Return Channel object
    def vec(self, ch):
        return self._vec.get(ch)

    # Return valid indicator
    def valid(self):
        return self._valid

    # Return timestamp of starting of last measurement circle
    def ts_start(self):
        return self._ts_start

    # Return timestamp of completing of last measurement circle
    def ts_complete(self):
        return self._ts_complete

    # Clean-up
    def destroy(self):
        for ch in self._sorted_ch_nums.copy():
            self.rem_ch(num=ch)

###
### Signal handler
###
def signal_handler(signal, frame):
    dbg('Signal caught: ' + str(signal))
    return

###
### Cleanup
###
def cleanup():
    dbg('Clean-up called')
    sys.stderr.write('INFO: Clean-up\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    ch_list.destroy()
    poller.close()
    os.close(pipe_r)
    os.close(pipe_w)
    if debug:
        debug_fileobj.close()
    sock.close()

###
### Run measure circle
###
def run_measure_circle(print_table=False):

    # Run measure circle
    if ch_list.measure():
        sys.stderr.write('ERROR: Measure circle failed\n')

    # Print channel values
    elif print_table:
        valid, ts_start, ts_complete, last_values = ch_list.last()
        if valid:
            ts_string = time.strftime(TS_FORMAT, time.localtime(ts_complete))
            ts_fraction = int(round(math.modf(ts_complete)[0], 6) * 1000000)
            ts_diff = round((ts_complete - ts_start) * 1000000)
            sys.stdout.write('{}.{:06d}, {:7d} us, '.format(ts_string, ts_fraction, ts_diff))
            for ch in sorted_channels:
                valid, last, ts = last_values[ch]
                if valid:
                    sys.stdout.write('{}: {:+.2f}, '.format(channels_conf[ch], last/1000))
                else:
                    sys.stdout.write('{}:  Nan '.format(channels_conf[ch]))
            sys.stdout.write('\n')

###
### Process request
###
def process_message(data, client_address):
    global in_pkts_total, in_pkts_valid, in_pkts_bad, in_pkts_bad_ver, in_pkts_bad_len, in_pkts_bad_cmd
    global out_pkts_total, out_pkts_success, out_pkts_failed

    in_pkts_total += 1

    # Check if message header has correct length
    if len(data) < PROTO_HDRSIZ:
        in_pkts_bad += 1
        in_pkts_bad_len += 1
        return

    # Parse message header
    start = 0
    ver, authtype, unused, cmd = struct.unpack('>BBBB', data[start:PROTO_HDRSIZ])
    start += PROTO_HDRSIZ
    if ver != PROTO_VER:
        in_pkts_bad += 1
        in_pkts_bad_ver += 1
        return

    # Received request for last values
    if cmd == PROTO_CMD_GETLAST:
        if data[start:]:
            in_pkts_bad += 1
            in_pkts_bad_len += 1
        else:
            in_pkts_valid += 1

            # Prepare last values
            valid, ts_start, ts_complete, last_values = ch_list.last()
            retlast_pdu = retlast_hdr
            retlast_pdu += struct.pack('>BBdd', len(sorted_channels), valid, ts_start, ts_complete)
            for ch in sorted_channels:
                valid, last, ts = last_values[ch]
                retlast_pdu += struct.pack('>BBLd', ch, valid, last, ts)
            retlast_len = len(retlast_pdu)

            # Send PDU with last values
            try:
                sent = sock.sendto(retlast_pdu, client_address)
                out_pkts_total += 1
                if sent == retlast_len:
                    out_pkts_success += 1
                else:
                    out_pkts_failed += 1
            except OSError as err:
                sys.stderr.write('Error sending to "{}:{}": {0}\n'.format(client_address[0], client_address[1], err))
                cleanup()
                sys.exit(1)
    else:
        in_pkts_bad += 1
        in_pkts_bad_cmd += 1

###
### Main program starts here
###

### Parse arguments
parser = argparse.ArgumentParser()
parser.add_argument('--server', '-s', help='name or address to bind to [single,optional]', default='')
parser.add_argument('--port', '-p', help='port number [single,optional]', default=DEF_PORT)
parser.add_argument('--minterval', '-m', help='measurement interval in seconds [single,optional]', type=int, default=DEF_MEASURE_INT)
parser.add_argument('--verbose', '-v', help='print extra messages [single,optional]', action='store_true', default=False)
parser.add_argument('--snmp-agent', '-a', help='act as SNMP agent [single,optional]', action='store_true', default=False)
parser.add_argument('--debug', '-d', help='debug output to file [single,optional]')
args = parser.parse_args()
bind_address = args.server
bind_port = args.port
mival = args.minterval
verbose = args.verbose
# SNMP agent
snmp_agent = args.snmp_agent
if snmp_agent:
    print_table = False
else:
    print_table = True
# Debug
if args.debug:
    debug = True
    debug_filename = args.debug
    try:
        debug_fileobj = open(debug_filename, mode='a')
    except OSError as err:
        sys.stderr.write('WARN: Error opening debug file "{}": {}\n'.format(debug_filename, err))
        debug = False
else:
    debug = False
dbg('Debug started')
dbg('Arguments: bind_address={}, bind_port={}, mival={}, verbose={}, snmp_agent={}, print_table={}'.format(
    bind_address, bind_port, mival, verbose, snmp_agent, print_table))

# We don't want to block while read from stdin if acting as ANMP agent
if snmp_agent:
    dbg('Setting stdin to non-blocking')
    stdin_fd = sys.stdin.fileno()
    flags = fcntl.fcntl(stdin_fd, fcntl.F_GETFL, 0)
    fcntl.fcntl(stdin_fd, fcntl.F_SETFL, flags | os.O_NONBLOCK)

# Check bind address
if bind_address:
    dbg('Getting IP address for "{}"'.format(bind_address))
    try:
        bind_address = socket.gethostbyname(bind_address)
    except OSError as err:
        sys.stderr.write('Error getting address for "{}": {0}\n'.format(bind_address, err))
        sys.exit(1)

# Create a UDP/IP socket
dbg('Opening non-blocking UDP/IP socket')
try:
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM | socket.SOCK_NONBLOCK)
    sock_fd = sock.fileno()
except OSError as err:
    sys.stderr.write('Error creating socket: {0}\n'.format(err))
    sys.exit(1)

# Bind the socket to the port
dbg('Binding socket fd={} to {}:{}'.format(sock_fd, bind_address, bind_port))
try:
    sock.bind((bind_address, bind_port))
except OSError as err:
    sock.close()
    sys.stderr.write('Error binding socket to "{}:{}": {0}\n'.format(bind_address, bind_port, err))
    sys.exit(1)

# Initialize statistics
in_pkts_total = 0
in_pkts_valid = 0
in_pkts_bad = 0
in_pkts_bad_ver = 0
in_pkts_bad_len = 0
in_pkts_bad_cmd = 0
out_pkts_total = 0
out_pkts_success = 0
out_pkts_failed = 0

# Initialize signal file descriptor
# We must set write end of pipe to non blocking mode
# Also we don't want to block while read signal numbers from read end
dbg('Creating pipe for catch signals and making its file descriptors non-blocking')
pipe_r, pipe_w = os.pipe()
flags = fcntl.fcntl(pipe_w, fcntl.F_GETFL, 0)
fcntl.fcntl(pipe_w, fcntl.F_SETFL, flags | os.O_NONBLOCK)
signal.set_wakeup_fd(pipe_w)
flags = fcntl.fcntl(pipe_r, fcntl.F_GETFL, 0)
fcntl.fcntl(pipe_r, fcntl.F_SETFL, flags | os.O_NONBLOCK)
dbg('Pipe created, pipe_r={}, pipe_w={}'.format(pipe_r, pipe_w))

# Redefine signal handlers
dbg('Redefining signal handlers')
signal.signal(signal.SIGALRM, signal_handler)
signal.signal(signal.SIGINT, signal_handler)
signal.signal(signal.SIGHUP, signal_handler)
signal.signal(signal.SIGTERM, signal_handler)

# Create poller and register file descriptors
dbg('Creating poller and register file descriptors')
poller = select.epoll()
poller.register(pipe_r, select.EPOLLIN)
poller.register(sock_fd, select.EPOLLIN)
if snmp_agent:
    poller.register(stdin_fd, select.EPOLLIN)

# Calculate coefficient
factor = VREF * (R_PU + R_PD) / R_PD

# Prepare header for RETLAST PDU
retlast_hdr = struct.pack('>BBBB', PROTO_VER, PROTO_AUTHTYPE_NONE, PROTO_UNUSED, PROTO_CMD_RETLAST)

# Initialize channel list
dbg('Start initializing channel list, {} channels in configuration'.format(len(channels_conf)))
sys.stderr.write('INFO: Initializing channels\n')
ch_list = ChannelList(factor=factor)
sorted_channels = sorted(channels_conf.keys())
for ch in sorted_channels:
    if ch_list.add_ch(num=ch, label=channels_conf[ch]):
        sys.stderr.write('ERROR: Failed to add channel number {}, label {}\n'.format(ch, channels_conf[ch]))
        sys.exit(1)
dbg('Channel list initialized, {} channels'.format(ch_list.num_of_channels()))

# Initialize MIB objects and list of OIDs
if snmp_agent:
    dbg('Start initializing MIB, base={}'.format(MIB_BASE))
    mib_init(ch_list)
    dbg('MIB initialized, {} variables'.format(len(mib)))

# Set interval timer
# Initial value of timer bounded to measurement interval
dbg('Setting interval timer, {} s'.format(mival))
t = time.time()
t_rest = mival - t % mival - MIVAL_SHIFT
if t_rest < 0:
    t_rest += mival
signal.setitimer(signal.ITIMER_REAL, t_rest, mival)

# Main loop
dbg('Starting main loop')
sys.stderr.write('INFO: Entering main loop\n')
while True:

    # Wait for events and process its
    try:
        dbg('Calling poller')
        events = poller.poll()
        dbg('Poller returned {} events'.format(len(events)))
    except InterruptedError:
        continue
    for fd, flags in events:
        dbg('Start processing event, fd={}, flags={}'.format(fd, flags))

        # Signal received, extract signal numbers from wakeup fd
        if fd == pipe_r and flags & select.EPOLLIN:
            dbg('Signal received from wakeup fd, unpacking signal numbers')
            data = os.read(pipe_r, SIG_WAKEUP_FD_RLEN)
            signums = struct.unpack('{}B'.format(len(data)), data)
            dbg('Signal numbers unpacked: {}'.format(signums))

            # Process signals
            for signum in signums:
                if signum == signal.SIGALRM:
                    dbg('Got SIGALRM, running measure circle')
                    run_measure_circle(print_table)
                elif signum == signal.SIGINT:
                    dbg('Got SIGINT, terminating')
                    sys.stderr.write('\nSIGINT received\n')
                    cleanup()
                    sys.exit(0)
                elif signum == signal.SIGTERM:
                    dbg('Got SIGTERM, terminating')
                    sys.stderr.write('\nSIGTERM received\n')
                    cleanup()
                    sys.exit(0)
                elif signum == signal.SIGHUP:
                    dbg('Got SIGHUP, ignoring')
                    sys.stderr.write('SIGHUP received\n')
                else:
                    dbg('Got uncaught signal {}, ignoring'.format(signum))
                    sys.stderr.write('ERROR: Unexpected signal received: {}\n'.format(signum))

        # Data available on stdin if acting as SNMP agent
        elif snmp_agent and fd == stdin_fd and flags & select.EPOLLIN:
            dbg('Data available on stdin, reading')
            lines = sys.stdin.readlines()
            dbg('Read {} lines from stdin: {}'.format(len(lines), repr(''.join(lines))))
            if not lines:
                sys.stderr.write('ERROR: Catched event on stdin but no lines read\n')
                continue
            first = lines.pop(0)

            # Handshake
            if first == 'PING\n':
                dbg('Got PING request, sending PONG reply')
                sys.stdout.write('PONG\n')
                sys.stdout.flush()
                sys.stderr.write('INFO: Passed PING/PONG handshake\n')

            # GET request
            elif first == 'get\n':
                dbg('Start processing GET request')
                if lines:
                    oid = lines.pop(0).rstrip('\n')
                    dbg('GET: Extracted OID: {}'.format(oid))
                    mibvar = find_mibvar(oid, mib)
                    # pdb.set_trace() ##### PDB TRACE POINT
                    if mibvar:
                        dbg('GET: Found MIBVar object')
                        if mibvar.get_max_access() < MIB_MAX_ACCESS_RO:
                            dbg('GET: MIBVar not accessible'.format(oid))
                            sys.stderr.write('WARN: MIB variable with OID {} not accessible\n'.format(oid))
                            sys.stdout.write('NONE\n')
                            sys.stdout.flush()
                        else:
                            dbg('GET: MIBVar accessible, trying to get value')
                            val = mibvar.get_value()
                            if val is not None:
                                dbg('GET: Got value of MIBVar, constructing reply')
                                syn = mibvar.get_syntax()
                                synname = MIB_SYNTAX_NAMES[syn]
                                reply = '{}\n{}\n{}\n'.format(oid, synname, str(val))
                                dbg('GET: Sending reply to stdout: {}'.format(repr(reply)))
                                sys.stdout.write(reply)
                                sys.stdout.flush()
                            else:
                                dbg('GET: Read of MIBVar failed')
                                sys.stderr.write('WARN: Read of MIB variable with OID {} returned None\n'.format(oid))
                                sys.stdout.write('NONE\n')
                                sys.stdout.flush()
                    else:
                        dbg('GET: MIBVar object not found')
                        sys.stderr.write('WARN: MIB variable with OID {} not existed\n'.format(oid))
                        sys.stdout.write('NONE\n')
                        sys.stdout.flush()
                else:
                    dbg('Malformed GET request')
                    sys.stderr.write('WARN: Malformed GET request, no OID\n')
                    sys.stdout.write('NONE\n')
                    sys.stdout.flush()

            # GETNEXT request
            elif first == 'getnext\n':
                dbg('Start processing GETNEXT request')
                if lines:
                    oid = lines.pop(0).rstrip('\n')
                    dbg('GETNEXT: Extracted OID: {}'.format(oid))
                    mibvar_next = find_mibvar_next(oid, mib, oids)
                    if mibvar_next:
                        dbg('GETNEXT: Found next MIBVar object, trying to get value')
                        val_next = mibvar_next.get_value()
                        if val_next is not None:
                            dbg('GETNEXT: Got value of next MIBVar, constructing reply')
                            oid_next = MIB_BASE + mibvar_next.get_oid()
                            syn_next = mibvar_next.get_syntax()
                            synname_next = MIB_SYNTAX_NAMES[syn_next]
                            reply = '{}\n{}\n{}\n'.format(oid_next, synname_next, str(val_next))
                            dbg('GETNEXT: Sending reply to stdout: {}'.format(repr(reply)))
                            sys.stdout.write(reply)
                            sys.stdout.flush()
                        else:
                            dbg('GETNEXT: Read of next MIBVar failed')
                            sys.stderr.write('WARN: Read of MIB variable with OID {} returned None\n'.format(oid_next))
                            sys.stdout.write('NONE\n')
                            sys.stdout.flush()
                    else:
                        dbg('GETNEXT: next MIBVar object not found')
                        sys.stderr.write('WARN: There is no accessible MIB variable next to OID {}\n'.format(oid))
                        sys.stdout.write('NONE\n')
                        sys.stdout.flush()
                else:
                    dbg('Malformed GETNEXT request')
                    sys.stderr.write('WARN: Malformed GETNEXT request, no OID\n')
                    sys.stdout.write('NONE\n')
                    sys.stdout.flush()

            # Unknown request
            else:
                dbg('Unrecognized request received on stdin')
                sys.stderr.write('ERROR: Unrecognized request received on stdin\n')
                sys.stdout.write('NONE\n')
                sys.stdout.flush()

        # Data available on socket
        elif fd == sock_fd and flags & select.EPOLLIN:
            dbg('Data available on socket, trying to read')
            try:
                data, client_address = sock.recvfrom(RECV_BUFSIZ)
            except OSError as err:
                dbg('Error receiving from socket "{}:{}": {0}'.format(bind_address, bind_port, err))
                sys.stderr.write('Error receiving from socket "{}:{}": {0}\n'.format(bind_address, bind_port, err))
                cleanup()
                sys.exit(1)

            # Process message
            if data:
                process_message(data, client_address)

        # Unexpected event
        else:
            sys.stderr.write('ERROR: Unexpected event on fd {}, flags {}\n'.format(fd, flags))

# This point should be never reached
# Cleanup and exit
cleanup()
sys.exit(0)
