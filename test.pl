#!/usr/bin/perl


use strict;
use File::Basename;

my $DIRECTORY_SEPARATOR = "/";

sub getOutputFileName
{
    # Get the hostname and the filepath of the shops file
    my $currentHostname = "SAMPi-North-Harrow";
    my $shopFilePath = "config/shops.csv";

    # File handles for the shops file
    my $shopIDFile;

    # Undef if not matched
    my $matchedID = undef;
    my $numberInHostname = undef;

    # Get the current date for use in the filename
    my @currentDate = getCurrentDate();

    # Open the shops file in read mode
    ## no critic qw(RequireBriefOpen)
    unless (open ($shopIDFile, '<', "config/shops.csv"))
    {
        logMsg("Error opening $shopFilePath: $!");
        die "Error opening $shopFilePath: $!";
    }

    # Iterate through shops and shop IDs
    while (my $row = <$shopIDFile>)
    {
        chomp($row); # Remove blank lines

        (my $shopID, my $shopName) = split(',', $row, 2);

        # Normalise the strings for comparison
        $shopName        = normaliseStr($shopName);
        $currentHostname = normaliseStr($currentHostname);

        # Check for a number in the hostname
        if ($currentHostname =~ m/(\d)/g)
        {
            # Store the result
            $numberInHostname = $1;

            # Remove the number from the hostname for now so shop ID matching works
            $currentHostname =~ s/\d//gx;
        }
    
        # Check if normalised hostname exactly matches normalised shop name
        if ($currentHostname =~ /^$shopName$/x)
        {
            $matchedID = $shopID;
            last;
        }
    }

    close $shopIDFile;

    # If we couldn't find a match, set $matchedID to "UNKNOWN" and log a warning
    unless ($matchedID)
    {
        $matchedID = "UNKNOWN";
        logMsg("No match found for '$currentHostname' in shops.csv, setting \$matchedID to 'UNKNOWN'");
    }

    # Otherwise, check if this is a store with multiple ECR units and append to the filename to avoid conflicts if so
    if ($matchedID ne "UNKNOWN" && $numberInHostname)
    {
        # This relies on the hostname having a number appended to it and no single-till stores having numbers in their hostname
        $matchedID .= "_$numberInHostname";
    }

    # Set the filename in the format "yyyymmdd_$matchedID.csv"
    my $outputFileName = dirname($0) . $DIRECTORY_SEPARATOR . "ecr_data" . $DIRECTORY_SEPARATOR .
       $currentDate[0] . $currentDate[1] . $currentDate[2] . "_$matchedID.csv";

    return $outputFileName;
}

# Utility function which returns the current date as an array in [yyyy][mm][dd] format
sub getCurrentDate
{
    my @timestamp = localtime();
    
    my $currentYear  = $timestamp[5] + 1900; # Need to add 1900 to get the current year
    my $currentMonth = $timestamp[4] + 1; # Months from localtime() are zero-indexed
    my $currentDay   = $timestamp[3];

    my @currentDate = ($currentYear, $currentMonth, sprintf("%02d", $currentDay)); # Pad day

    return @currentDate;
}

sub normaliseStr
{
    my ($rawString) = @_;

    # Remove blank spaces and the "SAMPi" prefix
    $rawString =~ s/[^\w]//gx;
    $rawString =~ s/SAMPi//igx;

    # Return lowercase representation
    return lc($rawString);
}

my $test =  getOutputFileName();

print "$test\n";

