import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1231 : checkSingleBlackFast (9, 20) 9995 .east (-3, -2) (-19, -19) = true := by
  decide +kernel

end LangtonsAnt
