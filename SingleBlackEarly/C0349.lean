import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0349 : checkSingleBlackFast (-5, 11) 12798 .south (-11, 4) (-24, -21) = true := by
  decide +kernel

end LangtonsAnt
