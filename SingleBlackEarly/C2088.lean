import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2088 : checkSingleBlackFast2 (-81, -59) 16937 .west (28, 37) (-57, 17) = true := by
  decide +kernel

end LangtonsAnt
