import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0502 : checkSingleBlackFast (-1, 13) 4068 .south (-9, -10) (-17, -10) = true := by
  decide +kernel

end LangtonsAnt
