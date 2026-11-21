import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0450 : checkSingleBlackFast (17, 8) 6018 .south (-11, -4) (-20, -13) = true := by
  decide +kernel

end LangtonsAnt
