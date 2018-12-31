# Fortsetzung

This is a tiny project whose goal is to explore patterns of programming
control flow using continuation passing style and callCC.

The main example is a naive SAT solver that operates over arbitrary symbolic
boolean expressions, making (mostly) arbitrary decisions and backtracking when
they are inconsistent. This style avoids the need to explicitly pass around
or mutate an assignment state.
