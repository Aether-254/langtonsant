import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1046 : checkSingleBlackFast2 (-13, -4) 15878 .south (-16, -2) (-33, -17) = true := by
  decide +kernel

end LangtonsAnt
