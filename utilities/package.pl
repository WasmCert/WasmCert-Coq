#!/usr/bin/perl
# To ease the generation of the COQPATH and VSCODESETTINGS in package.json
use strict ;
use warnings ;

my %packages = (
		iris => '#{coq-iris.install}/user-contrib',
		stdpp => '#{@opam/coq-stdpp.install}/user-contrib',
		mathcomp => '#{coq-mathcomp-ssreflect.install}/user-contrib',
		Flocq => '#{coq-flocq.install}/coq',
		compcert => '#{compcert.install}/coq',
		StrongInduction => '#{strong-induction.install}/lib/coq/user-contrib',
		parseque => '#{parseque.install}/lib/coq/user-contrib',
		ITree => '#{coq-itree.install}/user-contrib',
		ExtLib => '#{coq-ext-lib.install}/user-contrib',
		Paco => '#{coq-paco.install}/user-contrib'
	) ;

my $coqpath = "./theories" ;
foreach my $key (sort keys %packages){
	$coqpath .= ':' . $packages{$key} ;
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
foreach my $key (sort keys %packages){
	$vscodesettings .= '\\"-R\\",\\"' . $packages{$key} . '\\",\\"' . $key . '\\",' ;
}
$vscodesettings .= $vscodesettings_suffix ;

print '"VSCODESETTINGS": "' . $vscodesettings . '"' . "\n" ;

