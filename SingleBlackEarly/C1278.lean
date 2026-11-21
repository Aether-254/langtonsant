import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1278 : checkSingleBlackFast (0, 22) 10219 .east (-3, -2) (-19, -19) = true := by
  decide +kernel

end LangtonsAnt
