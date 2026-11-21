import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0439 : checkSingleBlackFast (16, 4) 4410 .south (-12, -10) (-17, -13) = true := by
  decide +kernel

end LangtonsAnt
