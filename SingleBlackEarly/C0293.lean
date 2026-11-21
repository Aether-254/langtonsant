import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0293 : checkSingleBlackFast (9, 12) 12665 .east (-20, -16) (-20, -11) = true := by
  decide +kernel

end LangtonsAnt
