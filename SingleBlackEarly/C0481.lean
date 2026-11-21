import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0481 : checkSingleBlackFast (10, 15) 31388 .south (-21, -11) (-43, -9) = true := by
  decide +kernel

end LangtonsAnt
