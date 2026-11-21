import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0383 : checkSingleBlackFast (15, 2) 5380 .south (-9, -11) (-17, -17) = true := by
  decide +kernel

end LangtonsAnt
