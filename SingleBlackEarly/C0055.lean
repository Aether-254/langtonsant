import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0055 : checkSingleBlackFast (4, -1) 1132 .south (-5, -7) (-11, -5) = true := by
  decide +kernel

end LangtonsAnt
