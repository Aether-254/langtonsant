import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0373 : checkSingleBlackFast (14, -4) 4114 .south (-12, -5) (-17, -4) = true := by
  decide +kernel

end LangtonsAnt
