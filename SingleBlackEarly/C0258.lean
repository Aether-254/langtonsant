import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0258 : checkSingleBlackFast (11, 10) 4359 .east (-5, 0) (-13, -13) = true := by
  decide +kernel

end LangtonsAnt
