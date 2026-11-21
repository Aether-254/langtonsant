import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1240 : checkSingleBlackFast (9, 16) 10123 .east (-3, -1) (-20, -19) = true := by
  decide +kernel

end LangtonsAnt
