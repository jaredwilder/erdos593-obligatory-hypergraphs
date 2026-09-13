/-
Erdős 593 campaign — AXIOM AUDIT.

`#print axioms` over every banked result of the campaign. A `sorryAx` anywhere in this output
invalidates the corresponding claim. The only axioms permitted are Lean's own three:
`propext`, `Classical.choice`, `Quot.sound`.

Reproduce (on the Lean box):
  /root/e593/build.sh Erdos593Frontier
  /root/e593/build.sh Erdos593Forest
  /root/e593/build.sh Erdos593Audit
  cat /root/e593/Erdos593Audit.log
-/

import Erdos593Forest

namespace Erdos593

-- Section 2: the containment that separates Komjáth's condition from Property B.
#print axioms Erdos593.twoColorable_of_threePartite

-- Section 4: the witnesses.
#print axioms Erdos593.C3exp_threePartite
#print axioms Erdos593.C3exp_linear
#print axioms Erdos593.C3exp_twoColorable
#print axioms Erdos593.K4exp_twoColorable
#print axioms Erdos593.exists_third
#print axioms Erdos593.card_triple
#print axioms Erdos593.K4exp_not_threePartite
#print axioms Erdos593.K4exp_not_linear

-- Section 5: the correctness warning.
#print axioms Erdos593.sufficientDirection_false_of_EGH
#print axioms Erdos593.sufficientDirection_false_of_Komjath
#print axioms Erdos593.sufficientDirection_false_of_EHR
#print axioms Erdos593.characterization_false_of_EGH
#print axioms Erdos593.characterization_false_of_Komjath
#print axioms Erdos593.characterization_false_of_EHR
#print axioms Erdos593.necessaryDirection_true_of_Komjath

-- Section 6: the frontier.
#print axioms Erdos593.outer_containment_strict
#print axioms Erdos593.upper_containment_strict

-- Section 7: the unconditional obligatory instance.
#print axioms Erdos593.edges_nonempty_of_large_chromatic
#print axioms Erdos593.oneEdge_obligatory

-- Forest file: the lower edge.
#print axioms Erdos593.subset_foldr_union
#print axioms Erdos593.not_looseForest_of_all_heavy
#print axioms Erdos593.C4mem
#print axioms Erdos593.C4cases
#print axioms Erdos593.C4exp_threePartite
#print axioms Erdos593.C4exp_linear
#print axioms Erdos593.C4exp_twoColorable
#print axioms Erdos593.C4exp_not_looseForest
#print axioms Erdos593.lower_containment_strict
#print axioms Erdos593.frontier_pinned

end Erdos593
