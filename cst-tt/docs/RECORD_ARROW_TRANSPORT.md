# Record-Arrow Transport

`TTH-10` now has two formally separated levels.

1. The original non-strict statement transports a declared record preorder through a monotone map.
2. The strict C6-relevant statement requires the map to be strict on every realized source arrow step.

The positive model maps source records `0 < 1 < 2` to target records `10 < 12 < 14`. An exhaustive search over all `5^3 = 125` maps from three ordered source records to five target records finds exactly 10 maps that preserve both strict steps.

The central negative control is a constant map. It is non-strictly monotone but collapses strict record progress. Therefore non-strict monotonicity alone cannot certify a genuinely advancing target arrow.

This is a structural arrow audit only. Holonomy is neither assumed nor sufficient, and no phenomenal interpretation is made.
