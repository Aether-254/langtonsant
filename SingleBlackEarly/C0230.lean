import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0230 : checkSingleBlackFast (6, 10) 5388 .south (-2, -11) (-16, -15) = true := by
  decide +kernel

end LangtonsAnt
