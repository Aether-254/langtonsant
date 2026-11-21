import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0784 : checkSingleBlackFast (24, -10) 6090 .south (-16, 0) (-21, -1) = true := by
  decide +kernel

end LangtonsAnt
