#!/usr/bin/perl -w

# extract proof object from TSTP files in current dir

use strict;

my $omitreg = "Search stopped by max_proofs option";
my @files = `ls -R */*/*.s`;
mkdir "00ALL";

my $file;
foreach $file (@files)
{
    open(IN,$file);
    my @path = split '\/', $file;
    if($#path != 2) {die("Bad file name $file")};
    open(OUT,">00ALL/$path[1].s");
    my $spit = 0;
    while(<IN>)
    {
	if(/BEGINNING OF PROOF OBJECT/) { $spit = 1 };
	if($spit && !(/$omitreg/)) { print OUT substr($_, 1) };
	if(/END OF PROOF OBJECT/) { $spit = 0 };
    }
}
