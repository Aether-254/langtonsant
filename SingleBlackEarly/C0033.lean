import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0033 : checkSingleBlackFast (1, 4) 1348 .south (-7, -8) (-9, -6) = true := by
  decide +kernel

end LangtonsAnt
