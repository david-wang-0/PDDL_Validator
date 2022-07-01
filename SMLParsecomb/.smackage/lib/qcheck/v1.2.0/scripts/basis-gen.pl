#! /usr/bin/perl
use strict;

my $sigFile = shift @ARGV;
my $genFile = shift @ARGV;
my $testFile = shift @ARGV;

open(SIG, ">$sigFile") or die 'cannot write sig';
open(GEN, ">$genFile") or die 'cannot write gen';
open(TEST, ">$testFile") or die 'cannot write test';

print SIG <<EOF;
(* DO NOT EDIT -- Generated by basis-gen.pl *)
signature GENERATOR_SIG = sig
  include TEXT_GENERATOR
  val stream : stream
  structure DateTime : DATE_TIME_GENERATOR
EOF

print GEN <<EOF;
(* DO NOT EDIT -- Generated by basis-gen.pl *)
functor GeneratorFn(R : APPLICATIVE_RNG) : GENERATOR_SIG =
struct
  local
    structure Gen = BaseGeneratorFn(R)
    structure Gen = GenText(structure Gen=Gen structure Text=Text)
  in 
EOF

foreach my $mod (@ARGV)
{
    if($mod =~ /Int|Position/)
    {
        print SIG "structure $mod : INT_GENERATOR\n";
        print GEN "structure $mod = GenInt(open Gen structure Int = $mod)\n";
        print TEST "structure I = IntFromTo($mod)\n";
        print TEST "structure T = TestFromToString(open I val name=\"$mod\")\n";
    }
    elsif($mod =~ /Word/)
    {
        print SIG "structure $mod : WORD_GENERATOR\n";
        print GEN "structure $mod = GenWord(open Gen structure Word = $mod)\n";
    }
    elsif($mod =~ /Real/)
    {
        print SIG "structure $mod : REAL_GENERATOR\n";
        print GEN "structure $mod = GenReal(open Gen structure Real = $mod)\n";
    }
    elsif($mod =~ /Text/)
    {
        print SIG "structure $mod : PRETEXT_GENERATOR\n";
        print GEN "structure $mod = GenText(structure Gen=Gen structure Text=$mod)\n";
    }
    else
    {
        print "Skipping unrecognized module: $mod\n";
    }
}

print SIG "end\n";

print GEN <<EOF;
    structure DateTime = GenDateTime(Gen)
    open Gen
    val stream = start (R.new())
  end (* local *)
  type rand = R.rand
  type 'a gen = rand -> 'a * rand
  type ('a, 'b) co = 'a -> 'b gen -> 'b gen
end
structure RandGen = GeneratorFn(Rand)
EOF

close(SIG);
close(GEN);
close(TEST);
exit;
