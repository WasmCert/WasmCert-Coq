#!/usr/bin/env perl
# Fetches the markdown files in the tests/ folder, and execute them.
use strict ;
use warnings ;
use List::Util qw(any) ;
use Capture::Tiny qw(capture) ;

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
		# Any line not enclosed in a ``` block are ignored.

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
					my $negative = $false ;
					if ($line =~ /#.*\@negative/){
						$negative = $true ;
					}
					$line =~ s/\$([^#]*)(#[^\n]*)?\n/$1/ ;
					if ($line =~ /[^ ]/){
						push @commandLines, {
							cmd => $line,
							neg => $negative
						} ;
					}
				} else {
					$expectedResult .= $line ;
				}
			} else {
				if ($line =~ /^```/) {
					my ($lang) = $line =~ /^```(.*)\n$/s ;
					if ($lang eq ''){
						if (not $otherParsing){
							die "Unexpected end of quote (or quote-block without any declared language)" ;
						}
						$otherParsing = $false ;
					} else {
						if ($otherParsing){
							die "Nested quotes" ;
						}
						# We entered a ``` block, and we now check which language is declared.
						if (any { $lang eq $_ } ('sh', 'bash')){
							# This block is meant to be executed.
							$parsingShell = $true ;
						} elsif (any { $lang eq $_ } ('wasm', 'webassembly', 'ocaml', 'coq', 'text')){
							# This block is meant to be ignored.
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
		for my $cell (@commandLines){
			my $command = %$cell{cmd} ;
			my $negative = %$cell{neg};
			if ($negative){
				print "Running (meant to fail): $command\n" ;
			} else {
				print "Running: $command\n" ;
			}
			my $errcode = 0 ;
			my ($stdout, $stderr) = capture {
				$errcode = system "$command" ;
			} ;
			$actualResult .= $stdout ;
			my $ok = $true ;
			if ($errcode != 0){
				$ok = $false ;
			}
			if ($stderr ne ''){
				print "stderr output:\n$stderr\n" ;
				$ok = $false ;
			}
			if ($ok and $negative){
				die "Negative test did not fail"
			}
			if ((not $ok) and not $negative){
				my $message = 'unknown failure';
				if ($stderr ne ''){
					$message = "non-empty stderr output" ;
				}
				if ($errcode != 0){
					$message = '' . ($errcode >> 8) ;
					if ($errcode == -1){
						$message = "failed to execute" ;
					} elsif ($errcode & 127){
						$message = "signal " . ($errcode & 127) ;
						if ($errcode & 128){
							$message .= ", with coredump" ;
						}
					}
					$message = "error code: " . $message ;
				}
				die "Test failed (by $message)" ;
			}
		}

		# Before comparing the output, we change them to accept relaxed output.

		# Removing colors
		$actualResult =~ s/\e\[\d+m//g ;
		$expectedResult =~ s/\e\[\d+m//g ;

		# Dealing with escape sequences to delete characters
		$actualResult =~ s/\e\[0D//g ;
		$expectedResult =~ s/\e\[0D//g ;
		$actualResult =~ s/.\e\[1D//g ;
		$expectedResult =~ s/.\e\[1D//g ;
		$actualResult =~ s/..\e\[2D//g ;
		$expectedResult =~ s/..\e\[2D//g ;
		$actualResult =~ s/...\e\[3D//g ;
		$expectedResult =~ s/...\e\[3D//g ;
		$actualResult =~ s/....\e\[4D//g ;
		$expectedResult =~ s/....\e\[4D//g ;
		$actualResult =~ s/.....\e\[5D//g ;
		$expectedResult =~ s/.....\e\[5D//g ;

		# Removing trailing spaces and empty lines
		$actualResult .= "\n" ;
		$actualResult =~ s/[ \t\n\r]+\n/\n/g ;
		$actualResult = "\n" . $actualResult ;
		$actualResult =~ s/\n[ \t\n\r]+/\n/g ;
		$expectedResult .= "\n" ;
		$expectedResult =~ s/[ \t\n\r]+\n/\n/g ;
		$expectedResult = "\n" . $expectedResult ;
		$expectedResult =~ s/\n[ \t\n\r]+/\n/g ;

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

