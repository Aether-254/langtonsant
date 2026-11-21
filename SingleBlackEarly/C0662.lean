import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0662 : checkSingleBlackFast (13, -11) 7335 .east (-2, -5) (-16, -18) = true := by
  decide +kernel

end LangtonsAnt
