import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0538 : checkSingleBlackFast2 (7, -3) 10778 .south (-16, 1) (-23, -8) = true := by
  decide +kernel

end LangtonsAnt
