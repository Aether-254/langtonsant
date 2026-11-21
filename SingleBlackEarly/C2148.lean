import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2148 : checkSingleBlackFast2 (-88, -60) 18553 .west (37, 43) (-63, 20) = true := by
  decide +kernel

end LangtonsAnt
