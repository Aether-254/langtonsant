import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1950 : checkSingleBlackFast2 (-70, -42) 17617 .west (28, 34) (-54, 11) = true := by
  decide +kernel

end LangtonsAnt
