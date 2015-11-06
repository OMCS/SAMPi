#!/usr/bin/env perl

use warnings;
use strict;
use diagnostics;

use Data::Dumper;
use Term::ANSIColor;

my @lines;

open(my $csvFile, "<", "./config/shops.csv") or die;

local $/ = "\r\n"; # CRLF

while (my $line = <$csvFile>)
{
    chomp($line);
    push (@lines, split(',', $line, 2)) unless $line =~ /ID/x;
}

close $csvFile;

my %systems = map {reverse split /,/x} @lines;

foreach my $system (sort {$a <=> $b} keys %systems)
{
    print color("reset");
    # print "$systems{$system}: $system\n"; 
    print("Connecting to $systems{$system} ($system)...");
    my $status = system("netcat -z -w2 sampi$system.ddns.net 22 > /dev/null 2>&1");
    
    if ($status == 0)
    {
        print color("green"), "success\n";       
    }

    else
    {
        print color("red"), "failure\n";
    }
}

print color("reset");
