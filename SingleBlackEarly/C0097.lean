import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0097 : checkSingleBlackFast (2, 4) 952 .south (-6, -5) (-8, -5) = true := by
  decide +kernel

end LangtonsAnt
