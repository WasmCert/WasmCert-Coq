#!/usr/bin/perl
# Fetches the markdown files in the tests/ folder, and execute them.
use strict ;
use warnings ;
use experimental 'smartmatch';

my $false = 0 ;
my $true = 1 ;

my $testDirectory = "tests/" ;

print "Testing $testDirectory.\n" ;
opendir my $dir, $testDirectory or die "Issue openning the test folder" ;
my @files = readdir $dir ;

chdir $testDirectory ;

foreach my $file (@files){
	if ($file =~ /\.md$/) {
		print "Testing $file.\n" ;
		open (FILE, '<', $file) or die "Issue openning file $file" ;

		# First parsing what is expected.

		my $parsingShell = $false ;
		my $otherParsing = $false ;

		my @commandLines = () ; # All the commands to be run.
		my $expectedResult = '' ; # The expected result of these commands.

		while (<FILE>) {
			my $line = $_ ;
			if ($parsingShell) {
				if ($line =~ /^```\n?/){
					$parsingShell = $false ;
				} elsif ($line =~ /^\$\$/){
					$expectedResult .= substr $line, 1 ;
				} elsif ($line =~ /^\$/){
					push @commandLines, (substr $line, 1) ;
				} else {
					$expectedResult .= $line ;
				}
			} else {
				if ($line =~ /^```/) {
					my ($lang) = $line =~ /^```(.*)\n$/s ;
					if ($lang eq ''){
						if ($otherParsing != $true){
							die "Unexpected end of quote" ;
						}
						$otherParsing = $false ;
					} else {
						if ($otherParsing){
							die "Nested quotes" ;
						}
						if ($lang ~~ ['sh', 'bash']){
							$parsingShell = $true ;
						} elsif ($lang ~~ ['wasm', 'webassembly', 'ocaml', 'coq']){
							$otherParsing = $true ;
						} else {
							die "Unknown language: $lang" ;
						}
					}
				}
			}
		}

		if ($otherParsing or $parsingShell){
			die "Missing end of quote" ;
		}

		# Then running these commands.

		my $actualResult = '' ; # The result of all these commands.
		for my $command (@commandLines){
			print $command ;
			$actualResult .= `$command` ;
		}

		# Before comparing the output, we change them to accept relaxed output.

		# Removing colors
		$actualResult =~ s/\e\[\d+m//g ;
		$expectedResult =~ s/\e\[\d+m//g ;
		# Removing trailing spaces and empty lines
		$actualResult .= "\n" ;
		$actualResult =~ s/[ \n]+\n/\n/g ;
		$actualResult = "\n" . $actualResult ;
		$actualResult =~ s/\n[ \n]+/\n/g ;
		$expectedResult .= "\n" ;
		$expectedResult =~ s/[ \n]+\n/\n/g ;
		$expectedResult = "\n" . $expectedResult ;
		$expectedResult =~ s/\n[ \n]+/\n/g ;

		if ($actualResult ne $expectedResult){
			print "Expected output:$expectedResult" ;
			print "Actual output:$actualResult" ;
			die "Unexpected output"
		}

		close (FILE) ;
		print "Done.\n" ;
	}
}

closedir $dir ;
print "Done testing $testDirectory.\n" ;

