import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0059 : checkSingleBlackFast (-3, -3) 11034 .south (-5, -1) (-28, 2) = true := by
  decide +kernel

end LangtonsAnt
