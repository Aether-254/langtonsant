import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1066 : checkSingleBlackFast2 (-16, -2) 17914 .south (-8, -2) (-41, -17) = true := by
  decide +kernel

end LangtonsAnt
