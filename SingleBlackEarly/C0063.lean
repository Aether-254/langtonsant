import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0063 : checkSingleBlackFast (-5, -4) 4704 .north (0, 2) (-16, -12) = true := by
  decide +kernel

end LangtonsAnt
