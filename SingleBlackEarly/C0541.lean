import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0541 : checkSingleBlackFast (6, -5) 30712 .south (-8, -12) (-24, -28) = true := by
  decide +kernel

end LangtonsAnt
