import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0689 : checkSingleBlackFast (20, -11) 13258 .south (-15, 0) (-26, -17) = true := by
  decide +kernel

end LangtonsAnt
