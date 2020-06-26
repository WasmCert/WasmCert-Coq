#!/usr/bin/perl
# To ease the generation of the COQPATH and VSCODESETTINGS in package.json
use strict ;
use warnings ;

my %packages = (
		iris => '#{coq-iris.install}/user-contrib',
		stdpp => '#{@opam/coq-stdpp.install}/user-contrib',
		mathcomp => '#{coq-mathcomp-ssreflect.root}/mathcomp',
		Flocq => '#{coq-flocq.install}/coq',
		compcert => '#{compcert.root}',
		StrongInduction => '#{strong-induction.root}',
		parseque => '#{parseque.root}',
	) ;

my $coqpath = "" ;
foreach my $key (keys %packages){
	if ($coqpath eq ""){
		$coqpath .= $packages{$key} ;
	} else {
		$coqpath .= ':' . $packages{$key} ;
	}
}

print '"COQPATH": "' . $coqpath . '",' . "\n" ;

my $vscodesettings_prefix =
	'{\\"coqtop.binPath\\":'
	. '\\"#{@opam/coq.root}/bin\\",'
	. '\\"coqtop.args\\":['
	. '\\"-coqlib\\",\\"#{@opam/coq.root}\\",' ;
my $vscodesettings_suffix =
	'\\"-R\\",\\"#{self.root}/_build/default/theories\\",\\"\\"]}' ;

my $vscodesettings = "" ;

$vscodesettings .= $vscodesettings_prefix ;
foreach my $key (keys %packages){
	$vscodesettings .= '\\"-R\\",\\"' . $packages{$key} . '\\",\\"' . $key . '\\",' ;
}
$vscodesettings .= $vscodesettings_suffix ;

print '"VSCODESETTINGS": "' . $vscodesettings . '"' . "\n" ;

