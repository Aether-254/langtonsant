import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2085 : checkSingleBlackFast (-83, -55) 25945 .east (37, 25) (15, -60) = true := by
  decide +kernel

end LangtonsAnt
