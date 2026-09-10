import SequentialLearning.AbsorptionOracleResults

/-!
# Phase 4 absorption-oracle interface audit

The companion shell check verifies that the three exact manuscript-facing
wrappers expose the concrete absorption event and only the bundled RCD
existence assumption.  In particular, no branch-finiteness, branch-`L²`, or
binary-kernel implementation premise may reappear in these printed types.
-/

#check SequentialLearning.threeway
#check SequentialLearning.oraclestrict
#check SequentialLearning.oraclehilbert
