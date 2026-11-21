import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0362 : checkSingleBlackFast (13, 1) 5720 .south (-9, -11) (-17, -17) = true := by
  decide +kernel

end LangtonsAnt
