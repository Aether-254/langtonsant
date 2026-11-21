import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0903 : checkSingleBlackFast (-11, 10) 20843 .east (-5, -1) (-26, -27) = true := by
  decide +kernel

end LangtonsAnt
