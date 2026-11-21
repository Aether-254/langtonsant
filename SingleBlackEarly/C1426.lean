import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1426 : checkSingleBlackFast (-21, 4) 24715 .east (-3, -17) (-36, -17) = true := by
  decide +kernel

end LangtonsAnt
