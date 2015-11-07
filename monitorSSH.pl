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

my %SAMPiNodes = map {reverse split /,/x} @lines;

foreach my $node (sort {$a <=> $b} keys %SAMPiNodes)
{
    print color("reset");
    # print "$SAMPiNodes{$node}: $node\n"; 
    print("Connecting to $SAMPiNodes{$node} ($node)...");
    my $status = system("netcat -z -w2 sampi$node.ddns.net 22 > /dev/null 2>&1");
    
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
