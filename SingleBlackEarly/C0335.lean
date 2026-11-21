import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0335 : checkSingleBlackFast (2, 13) 3832 .south (-10, -10) (-16, -10) = true := by
  decide +kernel

end LangtonsAnt
