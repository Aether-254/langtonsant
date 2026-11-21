import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0843 : checkSingleBlackFast (-3, 15) 11832 .south (-6, -4) (-14, -20) = true := by
  decide +kernel

end LangtonsAnt
