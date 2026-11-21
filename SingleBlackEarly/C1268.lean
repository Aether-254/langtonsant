import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1268 : checkSingleBlackFast (4, 20) 10419 .east (-3, -2) (-19, -19) = true := by
  decide +kernel

end LangtonsAnt
