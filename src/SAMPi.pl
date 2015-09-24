#!/usr/bin/env perl
#
# SAMPi - SAM4S ECR Reader and Parser (Last Modified 25/09/2015)
#
# This software runs as a daemon on a suitably configured Raspberry Pi,
# reads from a connected SAM4S ECR via RS232, extracts various data
# in CSV format and stores it in preparation for upload via SFTP or a 
# another suitable protocol using SAMPi_UPLOAD.sh

use strict; 
use warnings;
use Readonly;

Readonly our $VERSION => 0.2;

# Logging
Readonly my $ENABLE_LOGGING => 1; # Enable or disable logging to file
my $logOpen = 0;
my $logFile;

# Serial Communications
use Device::SerialPort; 
my $serialPort;

# Simple function to print logging messages
# with a timestamp to a file and / or stdout 
sub logMsg
{
    # Take the message passed in as the first parameter and get the current time
    my $logMessage = shift;
    my $timestamp = localtime(time);

    # Write message to file if logging is enabled
    if ($ENABLE_LOGGING)
    {
        if ($logOpen == 0)
        {
            # Attempt to open the log file in append mode
            ## no critic qw(RequireBriefOpen)
            if (open $logFile, '>>', "SAMPi.log")
            {
                $logFile->autoflush(1); # Disable buffering
                $logOpen = 1;
            }

            # Print an error if unsuccessful 
            else
            {
                warn "Failed to open log file: $!\n";
                $logOpen = -1;
            }
        }

        if ($logOpen)
        {
            # Write message with timestamp to the log file
            print $logFile "$timestamp: $logMessage\n";
        }
    }

    # Print the message to STDOUT in any case
    print "$timestamp: $logMessage\n";

    return;
}

# This function initialises the serial port with the correct settings
# Modify this function if you require different settings 
sub initialiseSerialPort
{
    # 8N1 with software flow control by default
    #Readonly my $SERIAL_PORT => "/dev/ttyUSB0";
    Readonly my $SERIAL_PORT => "/dev/cu.Bluetooth-Incoming-Port";
    Readonly my $BPS => 9600;
    Readonly my $DATA_BITS => 8;
    Readonly my $STOP_BITS => 1;
    Readonly my $PARITY => "none";
    Readonly my $HANDSHAKE => "xoff";

    logMsg("Initialising Serial Port...");
    $serialPort = Device::SerialPort->new($SERIAL_PORT);

    # If there is an error initialising the serial port, print a warning and terminate
    if (!defined $serialPort)
    {
        logMsg("Error opening serial port $SERIAL_PORT: $!\n"); 
        die;
    }

    $serialPort->baudrate($BPS);
    $serialPort->databits($DATA_BITS);
    $serialPort->stopbits($STOP_BITS);
    $serialPort->parity($PARITY);
    $serialPort->handshake($HANDSHAKE);

    logMsg("Opened serial port $SERIAL_PORT at $BPS" . "BPS");

    return;
}

# This function reads serial data from the ECR using the connection established by initialiseSerialPort()
sub readSerialData
{
    if (!$serialPort)
    {
        croak("Serial port has not been configured, call initialiseSerialPort() before this function");
    }

    Readonly my $DATA_SIZE_BYTES => 256;
    Readonly my $READ_DELAY_SECONDS => 2000;

    while (1)
    {
        $serialPort->read_char_time(0); # Read characters as they are received
        $serialPort->read_const_time($READ_DELAY_SECONDS); # Time to wait between read calls 
         
        # Read a number of characters from the serial port
        my ($bytesReceived, $serialData) = $serialPort->read($DATA_SIZE_BYTES);
            
        if ($bytesReceived > 0)
        {
            # Print data received from ECR via serial
            print $serialData;
        }

        else
        {
            printf "%s seconds passed\n", $READ_DELAY_SECONDS / 1000;
        }
    }

    return;
}

# Main function
sub main
{
    logMsg("SAMPi v$VERSION Initialising...");
    initialiseSerialPort();
    readSerialData();

    return;
}

main();

