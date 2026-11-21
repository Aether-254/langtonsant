import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1978 : checkSingleBlackFast2 (-71, -49) 16417 .west (23, 32) (-52, 12) = true := by
  decide +kernel

end LangtonsAnt
