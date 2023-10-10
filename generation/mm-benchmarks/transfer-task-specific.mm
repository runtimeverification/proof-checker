$( 
  Declaration of Metamath constants
  Not needed if using Pi2 binary proof format
$)
$c #Pattern #EVar \imp ( ) |- \equals \rewrites $.
$c are-terms state $.
$c ge leq plus minus 10 100 200 90 210 1 0 $.

$(
  Declaration of metavariables of patterns
  Not needed if using Pi2 binary proof format
$)
$v A   $( account $)
   BF  $( balance_from $)
   BF' $( balance_from, after transfer $)
   BT  $( balence_to $)
   BT'  $( balence_to, after transfer $)
   R   $( return value (0 or 1) $)
$.
A-is-evar  $f #Pattern A $.   
BF-is-evar $f #Pattern BF $.  
BFp-is-evar $f #Pattern BF' $.  
BT-is-evar $f #Pattern BT $.  
BTp-is-evar $f #Pattern BT' $.  
R-is-evar  $f #Pattern R $.

$(
  Declaration of logical constructs, non-logical symbols 
  and literal values
$)
imp-is-pattern       $a #Pattern ( \imp BF BT ) $.
equals-is-pattern    $a #Pattern ( \equals BF BT ) $.
rewrites-is-pattern  $a #Pattern ( \rewrites BF BT ) $.
10-is-pattern        $a #Pattern 10 $.
100-is-pattern       $a #Pattern 100 $.
200-is-pattern       $a #Pattern 200 $.
90-is-pattern        $a #Pattern 90 $.
210-is-pattern       $a #Pattern 210 $.
1-is-pattern         $a #Pattern 1 $.
0-is-pattern         $a #Pattern 0 $.
are-terms-is-pattern $a #Pattern ( are-terms A BF BT R ) $.
state-is-pattern     $a #Pattern ( state A BF BT R ) $.
ge-is-pattern        $a #Pattern ( ge BF BT ) $.
leq-is-pattern       $a #Pattern ( leq BF BT ) $.
plus-is-pattern      $a #Pattern ( plus BF BT ) $.
minus-is-pattern     $a #Pattern ( minus BF BT ) $.

$( Rule #1 (then branch) $)
$( 
  Note that this rule is not triggered by the target
  exectuion trace and thus can be removed from the proof slice.
  Here I include this rule for reference.
$)
$(
${
  // the four pattenrs are terms (i.e., functional patterns)
  edge-1-term $e |- ( are-terms A BF BT R ) $.
  // A is greater than BF
  edge-1-cond $e |- ( ge A BF ) $.
  edge-1-step $a |- ( \rewrites ( state A BF BT R ) 
                                ( state A BF BT 0 ) ) $.
$}
$)

$( Rule #2 (else branch) $)
${
  $( the four pattenrs are terms (i.e., functional patterns) $)
  edge-2-term $e |- ( are-terms A BF BT R ) $.
  $( A is less than or equal to BF $)
  edge-2-cond $e |- ( leq A BF ) $.
  $( "whitelist" domain reasoning: BF' = BF - A $)
  edge-2-dv-1 $e |- ( \equals BF' ( minus BF A ) ) $.
  $( "whitelist" domain reasoning: BT' = BT + A $)
  edge-2-dv-2 $e |- ( \equals BT' ( plus BT A ) ) $.
  edge-2-step $a |- ( \rewrites ( state A BF BT R ) 
                                ( state A BF' BT' 1 ) ) $.
$}

$( 
  "Whitelist" assumptions about domain reasoning
  that are stored, logged, but not checked
$)

whitelist-dv-1 $a |- ( leq 10 100 ) $.
whitelist-dv-2 $a |- ( \equals 90 ( minus 100 10 ) ) $.
whitelist-dv-3 $a |- ( \equals 210 ( plus 200 10 ) ) $.
whitelist-dv-4 $a |- ( are-terms 10 100 200 0 ) $.

goal $p
  |- ( \rewrites ( state 10 100 200 0 ) ( state 10 90 210 1 ) ) 
$=
  ( 100-is-pattern 200-is-pattern 210-is-pattern whitelist-dv-4 whitelist-dv-1
  10-is-pattern 90-is-pattern 0-is-pattern whitelist-dv-2 whitelist-dv-3
  edge-2-step ) FAGBCHDEIJK $.
