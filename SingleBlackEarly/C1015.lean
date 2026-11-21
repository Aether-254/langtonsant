import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1015 : checkSingleBlackFast (-11, 7) 11194 .south (-11, -2) (-24, -15) = true := by
  decide +kernel

end LangtonsAnt
