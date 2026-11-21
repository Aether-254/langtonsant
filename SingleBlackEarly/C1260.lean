import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1260 : checkSingleBlackFast2 (6, 22) 10723 .east (-3, -5) (-16, -19) = true := by
  decide +kernel

end LangtonsAnt
