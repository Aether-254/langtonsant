import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1400 : checkSingleBlackFast2 (-20, 8) 19076 .south (-6, -9) (-16, -25) = true := by
  decide +kernel

end LangtonsAnt
