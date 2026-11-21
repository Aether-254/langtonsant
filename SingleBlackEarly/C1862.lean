import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1862 : checkSingleBlackFast2 (-62, -34) 17201 .west (24, 30) (-50, 7) = true := by
  decide +kernel

end LangtonsAnt
