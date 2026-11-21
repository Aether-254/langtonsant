import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0909 : checkSingleBlackFast (-9, 5) 13587 .east (-5, -8) (-27, -5) = true := by
  decide +kernel

end LangtonsAnt
