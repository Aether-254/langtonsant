import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0682 : checkSingleBlackFast2 (16, -9) 11032 .south (-9, -2) (-19, -16) = true := by
  decide +kernel

end LangtonsAnt
