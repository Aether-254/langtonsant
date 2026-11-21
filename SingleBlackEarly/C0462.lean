import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0462 : checkSingleBlackFast (17, 12) 4694 .south (-12, -9) (-17, -10) = true := by
  decide +kernel

end LangtonsAnt
